#!/usr/bin/env python3
"""Translate TeX line references of the submission (`3_5:1234`, `7_8:963-966`, `1_2:653`, ...)
into labels and numbers of the final paper.

The line numbers in Lean comments refer to the submission TeX in `paper/tex/`.  Labels are the
same in the final TeX (`paper/final/tex/`); numbers and pages come from the final PDF
(`paper/final/DubovaYangYauYin_RBM3D_Lean_version.pdf`) via `docs/claude-team/tools/paper-labels.tsv`.

Usage (from the repository root):
  python3 docs/claude-team/tools/texref.py 3_5:1234 7_8:963-966
  python3 docs/claude-team/tools/texref.py --scan RBM3D/Induction/Step1.lean [more .lean files]

For each reference it prints: the innermost labelled environment containing the line (kind,
number, label), "proof of <label>" when the line is inside a proof, the enclosing
(sub)section, and the nearest label above the line.  The suggestion is a starting point: read
the TeX around the line when the context is not clear.
"""
import re, sys, os, glob

ROOT = os.getcwd()
TEX = os.path.join(ROOT, 'paper', 'tex')
TSV = os.path.join(ROOT, 'docs', 'claude-team', 'tools', 'paper-labels.tsv')
STEMS = ['1_2', '3_5', '6', '7_8', 'A', 'B']
NUMBERED = {'theorem', 'lemma', 'proposition', 'corollary', 'definition', 'remark', 'claim',
            'example', 'assumption', 'strategy', 'equation', 'align', 'eqnarray', 'gather',
            'multline', 'figure', 'conjecture', 'notation'}

labels = {}
for line in open(TSV, encoding='utf-8'):
    if line.startswith('#') or not line.strip():
        continue
    lab, kind, num, page = line.rstrip('\n').split('\t')
    labels[lab] = (kind, num, page)

def show(lab):
    if lab is None:
        return '-'
    k = labels.get(lab)
    if not k:
        return f'`{lab}` (not in the final paper)'
    kind, num, page = k
    if kind == 'equation':
        return f'({num}) `{lab}` p.{page}'
    return f'{kind.capitalize()} {num} `{lab}` p.{page}'

_cache = {}
def parse(stem):
    if stem in _cache:
        return _cache[stem]
    fs = glob.glob(os.path.join(TEX, stem + '_*.tex'))
    if not fs:
        _cache[stem] = None
        return None
    lines = open(fs[0], encoding='utf-8', errors='replace').read().split('\n')
    info = []          # per line: (stack snapshot, proof_of, section_label, section_title, last_label)
    stack = []         # [env, label or None]
    last_closed = None # label of the last closed theorem-like env
    proof_of = []      # stack parallel to proofs
    sec_label = sec_title = None
    pending_sec = False
    last_label = None
    for ln in lines:
        code = re.sub(r'(?<!\\)%.*', '', ln)
        code = re.sub(r'\\be(?![a-zA-Z])', r'\\begin{equation}', code)
        code = re.sub(r'\\ee(?![a-zA-Z])', r'\\end{equation}', code)
        for m in re.finditer(r'\\(begin|end)\{([a-zA-Z*]+)\}|\\label\{([^}]*)\}|\\(section|subsection|subsubsection)\*?\{([^}]*)', code):
            if m.group(1) == 'begin':
                env = m.group(2).rstrip('*')
                stack.append([env, None])
                if env == 'proof':
                    proof_of.append(last_closed)
            elif m.group(1) == 'end':
                env = m.group(2).rstrip('*')
                for i in range(len(stack) - 1, -1, -1):
                    if stack[i][0] == env:
                        if env in NUMBERED and env not in ('equation', 'align', 'eqnarray', 'gather', 'multline', 'figure') and stack[i][1]:
                            last_closed = stack[i][1]
                        if env == 'proof' and proof_of:
                            proof_of.pop()
                        del stack[i:]
                        break
            elif m.group(3) is not None:
                lab = m.group(3)
                last_label = lab
                if pending_sec:
                    sec_label = lab
                    pending_sec = False
                else:
                    for i in range(len(stack) - 1, -1, -1):
                        if stack[i][0] in NUMBERED and stack[i][1] is None:
                            stack[i][1] = lab
                            break
            else:
                sec_title = m.group(5)
                sec_label = None
                pending_sec = True
        pending_sec = False   # a section label sits on the line of its \\section
        info.append(([tuple(s) for s in stack], proof_of[-1] if proof_of else None,
                     sec_label, sec_title, last_label))
    _cache[stem] = info
    return info

def resolve(stem, a):
    info = parse(stem)
    if info is None:
        return f'no TeX file paper/tex/{stem}_*.tex'
    if not (1 <= a <= len(info)):
        return f'line {a} out of range (1..{len(info)})'
    stack, pf, sl, st, ll = info[a - 1]
    inner = [s for s in stack if s[0] in NUMBERED and s[1]]
    parts = []
    if inner:
        parts.append('in ' + show(inner[-1][1]))
        if len(inner) > 1:
            parts.append('inside ' + show(inner[0][1]))
    if pf:
        parts.append('proof of ' + show(pf))
    parts.append('section "' + (st or '?') + '"' + (' ' + show(sl) if sl else ''))
    parts.append('nearest label above: ' + show(ll))
    return '; '.join(parts)

REF = re.compile(r'\b(1_2|3_5|6|7_8|A|B):([0-9]{1,5})(?:-([0-9]{1,5}))?')

def main(argv):
    if argv and argv[0] == '--scan':
        for path in argv[1:]:
            for n, ln in enumerate(open(path, encoding='utf-8'), 1):
                for m in REF.finditer(ln):
                    print(f'{path}:{n}: {m.group(0)} -> {resolve(m.group(1), int(m.group(2)))}')
        return
    for arg in argv:
        m = REF.fullmatch(arg)
        if not m:
            print(f'{arg}: not of the form <stem>:<line>[-<line>]')
            continue
        print(f'{arg} -> {resolve(m.group(1), int(m.group(2)))}')

if __name__ == '__main__':
    main(sys.argv[1:])
