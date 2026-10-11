"""ibpcost.py (T2402 1a): the layout check of the ticket (new file versus in-place edit of Green/IBP): line counts of the band declarations of RBM3D/Green/IBP.lean (code region, lines 73-1380)
that the diagonal BA display needs as class-G twins over D + seqHflow, and the two costs with the ratios of docs/reports/T2378-design.md section 1 (route formula: in place = edited fraction
0.15/0.24/0.30 of the lines used, twin = ratio 0.73/0.97/1.61).  Declaration ranges as in T2378 decls.py (docstring start to the line before the next declaration).
Usage: python3 ibpcost.py /path/to/RBM3D/Green/IBP.lean"""
import re, sys
lines = open(sys.argv[1]).read().split('\n')
start_re = re.compile(r'^(private )?(noncomputable )?(theorem|lemma|def|abbrev) (\S+)')
decl = [(i, m.group(4)) for i, l in enumerate(lines, 1) if (m := start_re.match(l)) and i < 1381]
rng = {}
for k, (i, name) in enumerate(decl):
    s = i; j = i - 2
    while j >= 0 and lines[j].strip() != '' and not lines[j].startswith(('end ', 'section', '/-!')):
        if lines[j].startswith('/--'): s = j + 1; break
        j -= 1
    e = (decl[k + 1][0] - 1) if k + 1 < len(decl) else 1380
    while e > i and (lines[e - 1].strip() == '' or lines[e - 1].startswith(('end ', 'section', 'variable', 'omit', '/-!', 'open'))): e -= 1
    rng[name] = (s, e)
twin = ['hasDerivAt_green_Hflow_update', 'tame_green_apply', 'entryCLM', 'hasDerivAt_green_apply_update', 'tame_green_mul_mul_green_apply',
        'tame_const_mul_green_apply', 'tame_const_mul_sandwich_apply', 'hasDerivAt_const_mul_green_apply_update', 'condRow_coord_mul_Bmat_mul_green_diag', 'condRow_Hflow_mul_green_diag',
        'Hflow_mul_apply_eq_sum', 'tame_Hflow_mul_green_apply', 'condExpDiag_eq_sum_Sblk', 'ibpRem', 'ibpRem_eq_add']
reuse = ['hasDerivAt_Hflow_update', 'sum_gvar_Bmat_sandwich_diag', 'sum_gvar_Bmat_sandwich_diag_mul', 'condRow_coord_mul', 'condRow_const_mul', 'condRow_neg_const_mul', 'condRow_finsetSum',
         'condRow_zero_apply', 'Bmat_mul_apply_diag_of_ne', 'condRow_tame_add', 'condRow_tame_sub', 'IBP_sum_svarF_row']
tot = 0
for n in twin:
    s, e = rng[n]; tot += e - s + 1; print(f"  twin   {n:46s} {s:5d}-{e:5d} {e - s + 1:4d}")
print(f"twin set: {tot} band lines (of 1024 class-G lines of the group C row)")
print("reused unchanged (statements free of `green`; public): " + ", ".join(f"{n} {rng[n][0]}-{rng[n][1]}" for n in reuse))
for lab, f in (('lo', (0.15, 0.73)), ('central', (0.24, 0.97)), ('hi', (0.30, 1.61))):
    print(f"  {lab:8s} in place = {tot * f[0]:6.0f}   new file (twin) = {tot * f[1]:6.0f}   difference = {tot * (f[1] - f[0]):6.0f}")
