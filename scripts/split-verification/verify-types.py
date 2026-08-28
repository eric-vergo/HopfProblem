import re, sys
W='/private/tmp/claude-501/-Users-eric-Documents-GitHub-verso-workspace/6956f628-1d4c-4197-879c-1c5aac95b285/scratchpad/monolith-ref'
AUX = re.compile(r'\.(_proof_\d+(_\d+)?|_simp_\d+(_\d+)?|_abel_\d+(_\d+)?|match_\d+(_\d+)?(\..*)?|_eq_\d+|eq_\d+|eq_def|_unfold|_sunfold|splitter|congr_simp|_cstage.*|_closed_\d+|_rarg|_boxed|_lambda_\d+|_elambda_\d+|_spec_\d+|_redArg|_override|_sparseCasesOn_\d+|_aux_.*|_ind|proof_\d+)$')
def load(p):
    d = {}
    for l in open(p):
        parts = l.rstrip('\n').split('\t')
        if len(parts) < 3: continue
        n = re.sub(r'^_private\.[^.]+(\.[^.]+)*?\.0\.', '', parts[0])
        if AUX.search(n) or '_aux_' in n or '«' in n: continue
        d[n] = (parts[1], parts[2])
    return d
B = load(W+'/.types-before.txt'); A = load('/Users/eric/Documents/GitHub/verso-workspace/hopf-problem/.types-after.txt')
print('core constants before:', len(B), 'after:', len(A))
missing = sorted(set(B)-set(A)); extra = sorted(set(A)-set(B))
changed = sorted(n for n in B if n in A and B[n] != A[n])
print('missing:', len(missing), missing[:10]); print('extra:', len(extra), extra[:10])
print('TYPE-HASH CHANGED:', len(changed)); [print('  !', c, B[c], A[c]) for c in changed[:30]]
print('RESULT:', 'ALL STATEMENTS IDENTICAL' if not missing and not changed else 'DIFFERENCES FOUND')
