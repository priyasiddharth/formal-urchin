#!/usr/bin/env python3
"""Turn a Miri execution's event stream into an execution certificate.

The certificate records, per USER-function frame instance in Miri's entry
order, the branch outcomes of that execution: which arm every `switchInt`
took and whether every `assert` passed. The Lean seam
(src/conformance/lowering.lean) consumes it to lower loops and dynamic
branches to straight-line mirlite with runtime checks. Events are matched
by kind in execution order, never by block or local numbers (charon's
built MIR and Miri's runtime MIR number them differently).

The events come from formal-urchin's Miri fork (vendor/miri, observation
only, `machine::formal_urchin`): with FORMAL_URCHIN_EVENTS=FILE it writes
one JSON object per line -- frame push/pop, each `switchInt`/`assert` about
to run, the block a terminator entered, each `_N = ...` statement about to
run, and the active variants of enum arguments after fn-entry retags.
Miri's stderr still decides the outcome (UB, panic, ok).

Usage:
  miri_cert.py --events X.events --stderr miri.stderr --ullbc X.ullbc.json \
               --source prep/X.rs --out X.cert.json [--exit-status N] \
               [--flag -Zmiri-...]...
"""
import argparse
import json
import re
import sys

# the TEXT of a `term` event is the terminator kind (Debug), of an `assign`
# event the statement kind (Debug)
RE_SWITCH = re.compile(r"^switchInt\((.*?)\) -> \[(.*)\]\s*$")
RE_ASSERT = re.compile(r"^assert\((.*)\) -> \[success: bb(\d+)")
RE_ASSIGN = re.compile(r"^(_\d+) = (.*)$")
RE_TARGET = re.compile(r"(\d+|otherwise): bb(\d+)")


def strip_generics(s):
    """Remove balanced <...> groups."""
    out, depth = [], 0
    for ch in s:
        if ch == "<":
            depth += 1
        elif ch == ">":
            depth = max(0, depth - 1)
        elif depth == 0:
            out.append(ch)
    return "".join(out)


def last_segment(path):
    # a turbofish frame (`safe::split_at_mut::<i32>`) strips to a trailing
    # `::`, which is not a segment
    p = strip_generics(path).rstrip(": ")
    return p.split("::")[-1].strip()


def qualified_self(path):
    """`<Self as Trait>::rest` -> (Self, Trait); None for a plain path."""
    if not path.startswith("<"):
        return None
    depth = 0
    for i, ch in enumerate(path):
        if ch == "<":
            depth += 1
        elif ch == ">":
            depth -= 1
            if depth == 0:
                inner = path[1:i]
                break
    else:
        return None
    depth = 0
    for i in range(len(inner)):
        ch = inner[i]
        if ch == "<":
            depth += 1
        elif ch == ">":
            depth -= 1
        elif depth == 0 and inner.startswith(" as ", i):
            return inner[:i], inner[i + 4:]
    return inner, ""


def user_fns_of(ullbc):
    with open(ullbc) as f:
        d = json.load(f)
    decls = d.get("translated", d).get("fun_decls", [])
    if isinstance(decls, dict):
        decls = decls.get("vector") or next(iter(decls.values()))
    names = set()
    for fd in decls:
        body = fd.get("body") if fd else None
        # only functions charon translated with a body (`Unstructured`);
        # opaque std items (e.g. a tuple's `PartialEq::eq`) are not user frames
        if not isinstance(body, dict) or "Unstructured" not in body:
            continue
        idents = [e["Ident"][0] for e in fd.get("item_meta", {}).get("name", []) if "Ident" in e]
        if idents:
            names.add(idents[-1])
    return names


STD_CRATES = ("std::", "core::", "alloc::", "libc::")
PRIMITIVES = {"bool", "char", "str", "u8", "u16", "u32", "u64", "u128", "usize",
              "i8", "i16", "i32", "i64", "i128", "isize", "f32", "f64", "!"}


def is_std_type(t):
    """A std path, or a primitive / builtin type constructor (`usize`,
    `[T]`, `[T; N]`, `&T`, `*const T`, `(A, B)`, `fn(..)`): no user impl
    can be keyed on it alone."""
    t = strip_generics(t).strip()
    return t.startswith(STD_CRATES) or t in PRIMITIVES or \
        t.startswith(("[", "&", "*", "(", "fn(", "dyn "))


def is_user_frame(path, user_fns):
    if any(x in path for x in ("{closure#", "{constant#")):
        return False
    q = qualified_self(path)
    if q is not None:
        # `<Self as Trait>::f` is user code when the impl could only be the
        # user's: the self type or the trait is not a std one
        # (`<std::cell::Cell<i32> as main::Thing>::do_the_thing`)
        self_ty, trait = q
        if all(is_std_type(t) for t in (self_ty, trait) if t):
            return False
    elif strip_generics(path).startswith(STD_CRATES) or \
            any(x in strip_generics(path) for x in STD_CRATES):
        # judged on the path WITHOUT its generic arguments: a user method
        # instantiated at a std type (`Option::<std::cell::RefCell<bool>>::as_ref`)
        # is still user code
        return False
    return last_segment(path) in user_fns


class Frame:
    def __init__(self, path, user):
        self.path = path
        self.user = user
        self.events = []
        self.pending = None          # (kind, dict) awaiting the next executing block
        self.assigns = {}            # local -> list of rvalue texts (drop-flag classification)
        self.switched = set()        # locals switched on
        self.variants = []           # fn-entry argument enum variants

    def record_assign(self, local, rv):
        self.assigns.setdefault(local, []).append(rv.strip())

    def resolve(self, bb):
        if self.pending is None:
            return
        kind, ev = self.pending
        self.pending = None
        ev["next"] = bb
        if kind == "switch":
            arm = "otherwise"
            for v, tgt in ev["cases"]:
                if tgt == bb:
                    arm = str(v)
                    break
            if arm == "otherwise" and bb != ev["otherwise"]:
                raise SystemExit(f"switch at {ev['descr']!r}: next block bb{bb} is no target")
            ev["arm"] = arm
        else:
            ev["outcome"] = "success" if bb == ev["success"] else "panic"
        self.events.append(ev)

    def abandon(self, reason):
        """The log ended (or left the frame) with an event pending: Miri stopped
        inside it — a panic/UB path."""
        if self.pending is None:
            return
        kind, ev = self.pending
        self.pending = None
        ev["next"] = None
        if kind == "switch":
            raise SystemExit(f"switch left unresolved at {ev['descr']!r} ({reason})")
        ev["outcome"] = "panic"
        self.events.append(ev)

    def finish(self):
        # drop-flag switches: the discriminant local was only ever assigned
        # bool constants in this frame instance
        for ev in self.events:
            if ev["k"] != "switch":
                continue
            m = re.match(r"(?:move|copy) (_\d+)$", ev["discr"].strip())
            if not m:
                continue
            rvs = self.assigns.get(m.group(1))
            if rvs and all(rv in ("const true", "const false") for rv in rvs):
                ev["drop_flag"] = True


def is_box_drop_frame(path):
    """`<std::boxed::Box<T> as std::ops::Drop>::drop`: one Box's destructor
    (after its contents were dropped; it frees the allocation unless T is
    zero-sized)."""
    q = qualified_self(path)
    return (q is not None and q[0].startswith("std::boxed::Box<")
            and strip_generics(q[1]) == "std::ops::Drop"
            and last_segment(path) == "drop")


def parse_events(events, user_fns):
    stack = []
    frames = []          # user frame instances in entry order
    for ev in events:
        k = ev["e"]
        if k == "push":
            path = ev["fn"].strip()
            if is_box_drop_frame(path):
                # a `drop` event in the innermost USER frame (a drop inside
                # `mem::drop` or other std code belongs to its user caller);
                # nested Boxes drop innermost first
                owner = next((f for f in reversed(stack) if f.user), None)
                if owner is not None:
                    q = qualified_self(path)
                    owner.events.append({"k": "drop", "ty": q[0][len("std::boxed::"):],
                                         "descr": path})
            fr = Frame(path, is_user_frame(path, user_fns))
            if stack and stack[-1].pending is not None:
                # a call cannot follow a switch/assert directly except via the
                # panic machinery: the pending assert did not succeed
                stack[-1].abandon("callee frame pushed before the next block")
            stack.append(fr)
            if fr.user:
                frames.append(fr)
            continue
        if k == "pop":
            if stack:
                fr = stack.pop()
                fr.abandon("frame popped")
                fr.finish()
            continue
        if not stack:
            continue
        top = stack[-1]
        if k == "enter":
            top.resolve(ev["bb"])
            continue
        if not top.user:
            continue
        if k == "variant":
            path = [int(x) for x in ev["path"].split(".") if x != ""]
            top.variants.append({"arg": ev["arg"], "path": path,
                                 "variant": ev["variant"], "ty": ev["ty"].strip()})
        elif k == "term":
            t = ev["t"].strip()
            m = RE_SWITCH.match(t)
            if m:
                targets = RE_TARGET.findall(m.group(2))
                cases = [(int(v), int(b)) for v, b in targets if v != "otherwise"]
                other = [int(b) for v, b in targets if v == "otherwise"]
                if len(other) != 1:
                    raise SystemExit(f"switch without a single otherwise: {t!r}")
                top.switched.add(m.group(1).strip())
                top.pending = ("switch", {"k": "switch", "discr": m.group(1).strip(),
                                           "cases": cases, "otherwise": other[0],
                                           "descr": t})
                continue
            m = RE_ASSERT.match(t)
            if m:
                top.pending = ("assert", {"k": "assert", "cond": m.group(1).split(",")[0].strip(),
                                           "success": int(m.group(2)), "descr": t})
                continue
            raise SystemExit(f"unexpected terminator event: {t!r}")
        elif k == "assign":
            m = RE_ASSIGN.match(ev["s"].strip())
            if m:
                top.record_assign(m.group(1), m.group(2))
    # the run ended: whatever is still open ended with Miri
    while stack:
        fr = stack.pop()
        fr.abandon("run ended")
        fr.finish()
    return frames


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--events", required=True)
    ap.add_argument("--stderr", required=True)
    ap.add_argument("--ullbc", required=True)
    ap.add_argument("--source", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--exit-status", type=int, default=0)
    ap.add_argument("--toolchain", default="nightly-2026-06-01")
    ap.add_argument("--flag", action="append", default=[])
    a = ap.parse_args()

    user_fns = user_fns_of(a.ullbc)
    with open(a.stderr, errors="replace") as f:
        text = f.read()
    if "error: Undefined Behavior" in text:
        outcome = "ub"
    elif "panicked at" in text or "error: abnormal termination" in text:
        outcome = "panic"
    elif a.exit_status == 0:
        outcome = "ok"
    else:
        raise SystemExit(f"miri exited {a.exit_status} without a recognisable UB/panic marker")

    with open(a.events) as f:
        events = [json.loads(l) for l in f if l.strip()]
    frames = parse_events(events, user_fns)
    if not frames:
        raise SystemExit("no user frames in the events (is user_fns right? is the Miri the fork?)")
    cert = {
        "version": 1,
        "source": a.source,
        "miri": {"toolchain": a.toolchain, "flags": ["-Zmir-opt-level=0"] + a.flag},
        "outcome": outcome,
        "user_fns": sorted(user_fns),
        "frames": [dict({"fn": last_segment(fr.path), "miri_path": fr.path, "events": fr.events},
                        **({"variants": fr.variants} if fr.variants else {}))
                   for fr in frames],
    }
    with open(a.out, "w") as f:
        json.dump(cert, f, indent=1)
        f.write("\n")
    n_ev = sum(len(fr.events) for fr in frames)
    print(f"{a.out}: outcome {outcome}, {len(frames)} user frames, {n_ev} events")


if __name__ == "__main__":
    main()
